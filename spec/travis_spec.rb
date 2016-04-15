require 'spec_helper'

describe 'metatheory::travis' do
  let(:chef_run) { ChefSpec::SoloRunner.new.converge(described_recipe) }

  it 'includes common' do
    expect(chef_run).to include_recipe('metatheory::common')
  end
end
