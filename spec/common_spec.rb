require 'spec_helper'

describe 'book::common' do
  let(:chef_run) { ChefSpec::SoloRunner.converge(described_recipe) }

  it 'includes infrastructure::common' do
    expect(chef_run).to include_recipe('infrastructure::common')
  end
end
